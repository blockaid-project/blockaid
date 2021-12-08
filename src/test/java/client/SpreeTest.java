package client;

import com.google.common.collect.ImmutableMap;
import org.junit.Test;

import java.sql.SQLException;

public class SpreeTest extends ApplicationTest {
    public SpreeTest() {
        super("spree_production", "spree", "12345678", "src/test/resources/SpreeTest");
    }

    private static final ImmutableMap<String, Object> PARAMS = ImmutableMap.of(
            "_STORE_URL_PATTERN", "%spree.internal%",
            "_MY_UID", 82000001,
            "_TOKEN", "0vm4Crp3w7avKavcKrjzow1637694716396"
    );

    @Test
    public void testAccountLink() throws ClassNotFoundException, SQLException {
        PQuery[] queries = new PQuery[]{
                new PQuery("SELECT `spree_stores`.`id`, `spree_stores`.`name`, `spree_stores`.`url`, `spree_stores`.`meta_description`, `spree_stores`.`meta_keywords`, `spree_stores`.`seo_title`, `spree_stores`.`mail_from_address`, `spree_stores`.`default_currency`, `spree_stores`.`code`, `spree_stores`.`default`, `spree_stores`.`created_at`, `spree_stores`.`updated_at`, `spree_stores`.`supported_currencies`, `spree_stores`.`facebook`, `spree_stores`.`twitter`, `spree_stores`.`instagram`, `spree_stores`.`default_locale`, `spree_stores`.`customer_support_email`, `spree_stores`.`default_country_id`, `spree_stores`.`description`, `spree_stores`.`address`, `spree_stores`.`contact_phone`, `spree_stores`.`checkout_zone_id`, `spree_stores`.`seo_robots`, `spree_stores`.`supported_locales` FROM `spree_stores` WHERE (url like '%spree.internal%') ORDER BY `spree_stores`.`created_at` ASC LIMIT ?", 1),
                new PQuery("SELECT `spree_users`.* FROM `spree_users` WHERE `spree_users`.`deleted_at` IS NULL AND `spree_users`.`id` = ? ORDER BY `spree_users`.`id` ASC LIMIT ?", 82000001, 1),
                new PQuery("SELECT 1 AS one FROM `spree_roles` INNER JOIN `spree_role_users` ON `spree_roles`.`id` = `spree_role_users`.`role_id` WHERE `spree_role_users`.`user_id` = ? AND `spree_roles`.`name` = ? LIMIT ?", 82000001, "admin", 1)
        };
        testQueries(queries, PARAMS, 1);
    }

    @Test
    public void testApiTokens() throws ClassNotFoundException, SQLException {
        PQuery[] queries = new PQuery[]{
                new PQuery("SELECT `spree_preferences`.* FROM `spree_preferences` WHERE `spree_preferences`.`key` = ? LIMIT ?", "spree/frontend_configuration/locale", 1),
                new PQuery("SELECT `spree_stores`.`id`, `spree_stores`.`name`, `spree_stores`.`url`, `spree_stores`.`meta_description`, `spree_stores`.`meta_keywords`, `spree_stores`.`seo_title`, `spree_stores`.`mail_from_address`, `spree_stores`.`default_currency`, `spree_stores`.`code`, `spree_stores`.`default`, `spree_stores`.`created_at`, `spree_stores`.`updated_at`, `spree_stores`.`supported_currencies`, `spree_stores`.`facebook`, `spree_stores`.`twitter`, `spree_stores`.`instagram`, `spree_stores`.`default_locale`, `spree_stores`.`customer_support_email`, `spree_stores`.`default_country_id`, `spree_stores`.`description`, `spree_stores`.`address`, `spree_stores`.`contact_phone`, `spree_stores`.`checkout_zone_id`, `spree_stores`.`seo_robots`, `spree_stores`.`supported_locales` FROM `spree_stores` WHERE (url like '%spree.internal%') ORDER BY `spree_stores`.`created_at` ASC LIMIT ?", 1),
                new PQuery("SELECT `spree_users`.* FROM `spree_users` WHERE `spree_users`.`deleted_at` IS NULL AND `spree_users`.`id` = ? ORDER BY `spree_users`.`id` ASC LIMIT ?", 82000001, 1),
                new PQuery("SELECT `spree_orders`.* FROM `spree_orders` WHERE `spree_orders`.`store_id` = ? AND `spree_orders`.`completed_at` IS NULL AND `spree_orders`.`currency` = ? AND `spree_orders`.`token` = ? LIMIT ?", 1, "USD", "0vm4Crp3w7avKavcKrjzow1637694716396", 1)
        };
        testQueries(queries, PARAMS, 1);
    }

    @Test
    public void testDiscontinuedProduct() throws ClassNotFoundException, SQLException {
        PQuery[] queries = new PQuery[]{
                new PQuery("SELECT `spree_preferences`.* FROM `spree_preferences` WHERE `spree_preferences`.`key` = ? LIMIT ?", "spree/frontend_configuration/locale", 1),
                new PQuery("SELECT `spree_stores`.`id`, `spree_stores`.`name`, `spree_stores`.`url`, `spree_stores`.`meta_description`, `spree_stores`.`meta_keywords`, `spree_stores`.`seo_title`, `spree_stores`.`mail_from_address`, `spree_stores`.`default_currency`, `spree_stores`.`code`, `spree_stores`.`default`, `spree_stores`.`created_at`, `spree_stores`.`updated_at`, `spree_stores`.`supported_currencies`, `spree_stores`.`facebook`, `spree_stores`.`twitter`, `spree_stores`.`instagram`, `spree_stores`.`default_locale`, `spree_stores`.`customer_support_email`, `spree_stores`.`default_country_id`, `spree_stores`.`description`, `spree_stores`.`address`, `spree_stores`.`contact_phone`, `spree_stores`.`checkout_zone_id`, `spree_stores`.`seo_robots`, `spree_stores`.`supported_locales` FROM `spree_stores` WHERE (url like '%spree.internal%') ORDER BY `spree_stores`.`created_at` ASC LIMIT ?", 1),
                new PQuery("SELECT `spree_users`.* FROM `spree_users` WHERE `spree_users`.`deleted_at` IS NULL AND `spree_users`.`id` = ? ORDER BY `spree_users`.`id` ASC LIMIT ?", 82000001, 1),
                new PQuery("SELECT 1 AS one FROM `spree_roles` INNER JOIN `spree_role_users` ON `spree_roles`.`id` = `spree_role_users`.`role_id` WHERE `spree_role_users`.`user_id` = ? AND `spree_roles`.`name` = ? LIMIT ?", 82000001, "admin", 1),
                new PQuery("SELECT `spree_products`.* FROM `spree_products` INNER JOIN `spree_products_stores` ON `spree_products`.`id` = `spree_products_stores`.`product_id` WHERE `spree_products`.`deleted_at` IS NULL AND `spree_products_stores`.`store_id` = ? AND (`spree_products`.deleted_at IS NULL or `spree_products`.deleted_at > '%1$s') AND (`spree_products`.discontinue_on IS NULL or `spree_products`.discontinue_on > '%1$s') AND (`spree_products`.available_on < '%1$s') AND `spree_products`.`slug` = ? LIMIT ?", 1, "checked-shirt", 1),
                new PQuery("SELECT `spree_products`.* FROM `spree_products` INNER JOIN `spree_products_stores` ON `spree_products`.`id` = `spree_products_stores`.`product_id` INNER JOIN `friendly_id_slugs` ON `friendly_id_slugs`.`deleted_at` IS NULL AND `friendly_id_slugs`.`sluggable_type` = ? AND `friendly_id_slugs`.`sluggable_id` = `spree_products`.`id` WHERE `spree_products`.`deleted_at` IS NULL AND `spree_products_stores`.`store_id` = ? AND (`spree_products`.deleted_at IS NULL or `spree_products`.deleted_at > '%1$s') AND (`spree_products`.discontinue_on IS NULL or `spree_products`.discontinue_on > '%1$s') AND (`spree_products`.available_on < '%1$s') AND `friendly_id_slugs`.`sluggable_type` = 'Spree::Product' AND `friendly_id_slugs`.`slug` = 'checked-shirt' ORDER BY `friendly_id_slugs`.`id` DESC LIMIT ?", "Spree::Product", 1, 1)
        };
        testQueries(queries, PARAMS, 1);
    }

    @Test
    public void testCartLink() throws ClassNotFoundException, SQLException {
        PQuery[] queries = new PQuery[]{
                new PQuery("CHECK CACHE READ views/spree/shared/_link_to_cart:02fae538495b085116c5c1b2466ca61a/en/USD/true/false/cart-indicator/3"),
        };
        testQueries(queries, PARAMS, 1);
    }

    @Test
    public void testHeaderCache() throws ClassNotFoundException, SQLException {
        PQuery[] queries = new PQuery[]{
                new PQuery("CHECK CACHE READ views/spree/shared/_header:ef00093092925391c81fde59f510cf2f/3ae3e1810eb0dd6bef02145e5e7fece6"),
        };
        testQueries(queries, PARAMS, 1);
    }

    @Test
    public void testAvailableProduct() throws ClassNotFoundException, SQLException {
        PQuery[] queries = new PQuery[]{
                new PQuery("SELECT `spree_preferences`.* FROM `spree_preferences` WHERE `spree_preferences`.`key` = ? LIMIT ?", "spree/frontend_configuration/locale", 1),
                new PQuery("SELECT `spree_stores`.`id`, `spree_stores`.`name`, `spree_stores`.`url`, `spree_stores`.`meta_description`, `spree_stores`.`meta_keywords`, `spree_stores`.`seo_title`, `spree_stores`.`mail_from_address`, `spree_stores`.`default_currency`, `spree_stores`.`code`, `spree_stores`.`default`, `spree_stores`.`created_at`, `spree_stores`.`updated_at`, `spree_stores`.`supported_currencies`, `spree_stores`.`facebook`, `spree_stores`.`twitter`, `spree_stores`.`instagram`, `spree_stores`.`default_locale`, `spree_stores`.`customer_support_email`, `spree_stores`.`default_country_id`, `spree_stores`.`description`, `spree_stores`.`address`, `spree_stores`.`contact_phone`, `spree_stores`.`checkout_zone_id`, `spree_stores`.`seo_robots`, `spree_stores`.`supported_locales` FROM `spree_stores` WHERE (url like '%spree.internal%') ORDER BY `spree_stores`.`created_at` ASC LIMIT ?", 1),
                new PQuery("SELECT `spree_users`.* FROM `spree_users` WHERE `spree_users`.`deleted_at` IS NULL AND `spree_users`.`id` = ? ORDER BY `spree_users`.`id` ASC LIMIT ?", 82000001, 1),
                new PQuery("SELECT 1 AS one FROM `spree_roles` INNER JOIN `spree_role_users` ON `spree_roles`.`id` = `spree_role_users`.`role_id` WHERE `spree_role_users`.`user_id` = ? AND `spree_roles`.`name` = ? LIMIT ?", 82000001, "admin", 1),
                new PQuery("SELECT `spree_products`.* FROM `spree_products` INNER JOIN `spree_products_stores` ON `spree_products`.`id` = `spree_products_stores`.`product_id` WHERE `spree_products`.`deleted_at` IS NULL AND `spree_products_stores`.`store_id` = ? AND (`spree_products`.deleted_at IS NULL or `spree_products`.deleted_at >= '%1$s') AND (`spree_products`.discontinue_on IS NULL or `spree_products`.discontinue_on >= '%1$s') AND (`spree_products`.available_on <= '%1$s') AND `spree_products`.`slug` = ? LIMIT ?", 1, "polo-t-shirt", 1),
                new PQuery("SELECT 1 AS one FROM `spree_stores` INNER JOIN `spree_products_stores` ON `spree_stores`.`id` = `spree_products_stores`.`store_id` WHERE `spree_products_stores`.`product_id` = ? AND `spree_stores`.`id` = ? LIMIT ?", 35000011, 1, 1),
                new PQuery("SELECT `spree_taxons`.* FROM `spree_taxons` INNER JOIN `spree_products_taxons` ON `spree_taxons`.`id` = `spree_products_taxons`.`taxon_id` WHERE `spree_products_taxons`.`product_id` = ? ORDER BY `spree_taxons`.`id` ASC LIMIT ?", 35000011, 1),
                new PQuery("SELECT `spree_preferences`.* FROM `spree_preferences` WHERE `spree_preferences`.`key` = ? LIMIT ?", "spree/frontend_configuration/http_cache_enabled", 1),
                new PQuery("SELECT `spree_promotions`.`id` FROM `spree_promotions` INNER JOIN `spree_promotion_rules` ON `spree_promotions`.`id` = `spree_promotion_rules`.`promotion_id` INNER JOIN `spree_product_promotion_rules` ON `spree_promotion_rules`.`id` = `spree_product_promotion_rules`.`promotion_rule_id` WHERE `spree_product_promotion_rules`.`product_id` = ? AND `spree_promotions`.`advertise` = ? AND (spree_promotions.starts_at IS NULL OR spree_promotions.starts_at <= '%1$s') AND (spree_promotions.expires_at IS NULL OR spree_promotions.expires_at >= '%1$s')", 35000011, true),
                new PQuery("SELECT DISTINCT `spree_variants`.* FROM `spree_variants` INNER JOIN `spree_prices` ON `spree_prices`.`deleted_at` IS NULL AND `spree_prices`.`variant_id` = `spree_variants`.`id` WHERE `spree_variants`.`deleted_at` IS NULL AND `spree_variants`.`product_id` = ? AND (`spree_variants`.`discontinue_on` IS NULL OR `spree_variants`.`discontinue_on` >= '%1$s') AND (`spree_variants`.deleted_at IS NULL) AND (spree_prices.currency = 'USD') AND (spree_prices.amount IS NOT NULL) ORDER BY `spree_variants`.`position` ASC", 35000011),
                new PQuery("SELECT `spree_prices`.* FROM `spree_prices` WHERE `spree_prices`.`currency` = ? AND `spree_prices`.`variant_id` IN (?, ?)", "USD", 83000011, 83000127),
                new PQuery("SELECT `spree_taxons`.* FROM `spree_taxons` WHERE `spree_taxons`.`lft` <= 2 AND `spree_taxons`.`rgt` >= 11 AND (`spree_taxons`.`id` != 79000001) AND `spree_taxons`.`parent_id` IS NOT NULL ORDER BY `spree_taxons`.`lft` ASC"),
                new PQuery("SELECT `spree_taxons`.`id` FROM `spree_taxons` WHERE `spree_taxons`.`lft` >= 2 AND `spree_taxons`.`lft` < 11 ORDER BY `spree_taxons`.`lft` ASC"),
                new PQuery("CHECK CACHE READ views/spree/products/show:dbe9e72687ec06f0ed6839db0579af2b/en/USD/true/false/spree/products/35000011-20211123081639034012/"),
                new PQuery("CHECK CACHE READ spree/default-image/spree/products/35000011-20211201233934628638"),
//                new PQuery("""
//SELECT MAX(`spree_products`.`updated_at`)
//FROM `spree_products`
//         INNER JOIN `spree_products_stores` ON `spree_products`.`id` = `spree_products_stores`.`product_id`
//         INNER JOIN `spree_variants`
//                    ON `spree_variants`.`deleted_at` IS NULL AND `spree_variants`.`product_id` = `spree_products`.`id`
//         INNER JOIN `spree_prices`
//                    ON `spree_prices`.`deleted_at` IS NULL AND `spree_prices`.`variant_id` = `spree_variants`.`id`
//         INNER JOIN `spree_products_taxons` ON `spree_products_taxons`.`product_id` = `spree_products`.`id`
//WHERE `spree_products`.`deleted_at` IS NULL
//  AND `spree_products_stores`.`store_id` = ?
//  AND (`spree_products`.discontinue_on IS NULL or `spree_products`.discontinue_on > '%1$s')
//  AND (`spree_products`.available_on <= '%1$s')
//  AND `spree_prices`.`currency` = ?
//  AND `spree_prices`.`amount` IS NOT NULL
//  AND `spree_products_taxons`.`taxon_id` IN (?, ?, ?, ?, ?)
//        """, 1, "USD", 79000001, 79000004, 79000005, 79000006, 79000007),
//                new PQuery("""
//                            SELECT DISTINCT `spree_products`.* FROM `spree_products` INNER JOIN `spree_products_stores` ON `spree_products`.`id` = `spree_products_stores`.`product_id` INNER JOIN `spree_variants` ON `spree_variants`.`deleted_at` IS NULL AND `spree_variants`.`product_id` = `spree_products`.`id` INNER JOIN `spree_prices` ON `spree_prices`.`deleted_at` IS NULL AND `spree_prices`.`variant_id` = `spree_variants`.`id` INNER JOIN `spree_products_taxons` ON `spree_products_taxons`.`product_id` = `spree_products`.`id` WHERE `spree_products`.`deleted_at` IS NULL AND `spree_products_stores`.`store_id` = ? AND (`spree_products`.discontinue_on IS NULL or `spree_products`.discontinue_on > '%1$s') AND (`spree_products`.available_on <= '%1$s') AND `spree_prices`.`currency` = ? AND `spree_prices`.`amount` IS NOT NULL AND `spree_products_taxons`.`taxon_id` IN (?, ?, ?, ?, ?)
//                        """, 1, "USD", 79000001, 79000004, 79000005, 79000006, 79000007),
        };
        testQueries(queries, PARAMS, 1);
    }

    @Test
    public void testCart() throws ClassNotFoundException, SQLException {
        PQuery[] queries = new PQuery[]{
//                new PQuery("SELECT `spree_preferences`.* FROM `spree_preferences` WHERE `spree_preferences`.`key` = ? LIMIT ?", "spree/frontend_configuration/locale", 1),
                new PQuery("SELECT `spree_stores`.`id`, `spree_stores`.`name`, `spree_stores`.`url`, `spree_stores`.`meta_description`, `spree_stores`.`meta_keywords`, `spree_stores`.`seo_title`, `spree_stores`.`mail_from_address`, `spree_stores`.`default_currency`, `spree_stores`.`code`, `spree_stores`.`default`, `spree_stores`.`created_at`, `spree_stores`.`updated_at`, `spree_stores`.`supported_currencies`, `spree_stores`.`facebook`, `spree_stores`.`twitter`, `spree_stores`.`instagram`, `spree_stores`.`default_locale`, `spree_stores`.`customer_support_email`, `spree_stores`.`default_country_id`, `spree_stores`.`description`, `spree_stores`.`address`, `spree_stores`.`contact_phone`, `spree_stores`.`checkout_zone_id`, `spree_stores`.`seo_robots`, `spree_stores`.`supported_locales` FROM `spree_stores` WHERE (url like '%spree.internal%') ORDER BY `spree_stores`.`created_at` ASC LIMIT ?", 1),
                new PQuery("SELECT `spree_users`.* FROM `spree_users` WHERE `spree_users`.`deleted_at` IS NULL AND `spree_users`.`id` = ? ORDER BY `spree_users`.`id` ASC LIMIT ?", 82000001, 1),
//                new PQuery("SELECT `spree_orders`.* FROM `spree_orders` WHERE `spree_orders`.`store_id` = ? AND `spree_orders`.`completed_at` IS NULL AND `spree_orders`.`currency` = ? AND `spree_orders`.`token` = ? LIMIT ?", 1, "USD", "0vm4Crp3w7avKavcKrjzow1637694716396", 1),
//                new PQuery("SELECT `spree_line_items`.* FROM `spree_line_items` WHERE `spree_line_items`.`order_id` = ? ORDER BY `spree_line_items`.`created_at` ASC", 25000005),
//                new PQuery("SELECT `spree_variants`.* FROM `spree_variants` WHERE `spree_variants`.`id` IN (?, ?, ?)", 83000136, 83000191, 83000198),
//                new PQuery("SELECT `spree_assets`.* FROM `spree_assets` WHERE `spree_assets`.`viewable_type` = ? AND `spree_assets`.`viewable_id` IN (?, ?, ?) ORDER BY `spree_assets`.`position` ASC", "Spree::Variant", 83000136, 83000191, 83000198),
//                new PQuery("SELECT `spree_option_value_variants`.* FROM `spree_option_value_variants` WHERE `spree_option_value_variants`.`variant_id` IN (?, ?, ?)", 83000136, 83000191, 83000198),
//                new PQuery("SELECT `spree_option_values`.* FROM `spree_option_values` WHERE `spree_option_values`.`id` IN (?, ?, ?, ?)", 22000004, 22000022, 22000002, 22000000),
//                new PQuery("SELECT `spree_products`.* FROM `spree_products` WHERE `spree_products`.`id` IN (?, ?, ?)", 35000020, 35000075, 35000082),
//                new PQuery("SELECT `spree_adjustments`.* FROM `spree_adjustments` WHERE `spree_adjustments`.`adjustable_type` = ? AND `spree_adjustments`.`adjustable_id` = ? ORDER BY `spree_adjustments`.`created_at` ASC", "Spree::Order", 25000005),
//                new PQuery("SELECT `spree_orders`.* FROM `spree_orders` WHERE `spree_orders`.`user_id` = ? AND `spree_orders`.`completed_at` IS NULL AND `spree_orders`.`id` != ? AND `spree_orders`.`store_id` = ?", 82000001, 25000005, 1),
//                new PQuery("SELECT 1 AS one FROM `spree_roles` INNER JOIN `spree_role_users` ON `spree_roles`.`id` = `spree_role_users`.`role_id` WHERE `spree_role_users`.`user_id` = ? AND `spree_roles`.`name` = ? LIMIT ?", 82000001, "admin", 1),
//                new PQuery("SELECT `spree_users`.* FROM `spree_users` WHERE `spree_users`.`deleted_at` IS NULL AND `spree_users`.`id` = ? LIMIT ?", 82000001, 1),
//                new PQuery("SELECT `spree_variants`.* FROM `spree_variants` WHERE `spree_variants`.`deleted_at` IS NULL AND `spree_variants`.`product_id` = ? AND `spree_variants`.`is_master` = ? LIMIT ?", 35000020, true, 1),
//                new PQuery("SELECT 1 AS one FROM `spree_assets` WHERE `spree_assets`.`viewable_id` = ? AND `spree_assets`.`viewable_type` = ? LIMIT ?", 83000020, "Spree::Variant", 1),
//                new PQuery("SELECT `spree_assets`.* FROM `spree_assets` WHERE `spree_assets`.`viewable_id` = ? AND `spree_assets`.`viewable_type` = ? ORDER BY `spree_assets`.`position` ASC LIMIT ?", 83000020, "Spree::Variant", 1),
//                new PQuery("SELECT `active_storage_attachments`.* FROM `active_storage_attachments` WHERE `active_storage_attachments`.`record_type` = ? AND `active_storage_attachments`.`name` = ? AND `active_storage_attachments`.`record_id` = ?", "Spree::Asset", "attachment", 1),
//                new PQuery("SELECT `active_storage_blobs`.* FROM `active_storage_blobs` WHERE `active_storage_blobs`.`id` = ?", 1),
//                new PQuery("SELECT SUM(`spree_adjustments`.`amount`) FROM `spree_adjustments` WHERE `spree_adjustments`.`order_id` = ? AND `spree_adjustments`.`eligible` = ? AND (`spree_adjustments`.amount != 0) AND `spree_adjustments`.`source_type` = ? AND `spree_adjustments`.`adjustable_type` != ?", 25000005, true, "Spree::PromotionAction", "Spree::Shipment"),
                new PQuery("SELECT `spree_menus`.* FROM `spree_menus` WHERE `spree_menus`.`store_id` = ? AND `spree_menus`.`location` = ? AND `spree_menus`.`locale` = ? ORDER BY `spree_menus`.`created_at` ASC LIMIT ?", 1, "header", "en", 1),
                new PQuery("SELECT `spree_menu_items`.* FROM `spree_menu_items` WHERE `spree_menu_items`.`menu_id` = ? AND `spree_menu_items`.`parent_id` IS NULL LIMIT ?", 16000000, 1),
                new PQuery("SELECT `spree_menu_items`.* FROM `spree_menu_items` WHERE `spree_menu_items`.`parent_id` = ? ORDER BY `spree_menu_items`.`lft` ASC", 15000000),
                new PQuery("SELECT `spree_menu_items`.* FROM `spree_menu_items` WHERE `spree_menu_items`.`parent_id` = ? ORDER BY `spree_menu_items`.`lft` ASC", 15000012),
//                new PQuery("SELECT `spree_taxons`.* FROM `spree_taxons` WHERE `spree_taxons`.`id` = ? LIMIT ?", 79000002, 1),
                new PQuery("SELECT `spree_menu_items`.* FROM `spree_menu_items` WHERE `spree_menu_items`.`parent_id` = ? ORDER BY `spree_menu_items`.`lft` ASC", 15000015),
                new PQuery("SELECT `spree_taxons`.* FROM `spree_taxons` WHERE `spree_taxons`.`id` = ? LIMIT ?", 79000008, 1),
                new PQuery("SELECT `spree_menu_items`.* FROM `spree_menu_items` WHERE `spree_menu_items`.`parent_id` = ? ORDER BY `spree_menu_items`.`lft` ASC", 15000018),
                new PQuery("SELECT `spree_assets`.* FROM `spree_assets` WHERE `spree_assets`.`type` = ? AND `spree_assets`.`viewable_id` = ? AND `spree_assets`.`viewable_type` = ? LIMIT ?", "Spree::Icon", 15000021, "Spree::MenuItem", 1),
        };
        testQueries(queries, PARAMS, 1);
    }

    @Test
    public void testOrder() throws ClassNotFoundException, SQLException {
        PQuery[] queries = new PQuery[]{
//                new PQuery("CHECK CACHE READ spree/frontend_configuration/locale"),
//                new PQuery("SELECT `spree_preferences`.* FROM `spree_preferences` WHERE `spree_preferences`.`key` = ? LIMIT ?", "spree/frontend_configuration/locale", 1),
//                new PQuery("SELECT `spree_stores`.`id`, `spree_stores`.`name`, `spree_stores`.`url`, `spree_stores`.`meta_description`, `spree_stores`.`meta_keywords`, `spree_stores`.`seo_title`, `spree_stores`.`mail_from_address`, `spree_stores`.`default_currency`, `spree_stores`.`code`, `spree_stores`.`default`, `spree_stores`.`created_at`, `spree_stores`.`updated_at`, `spree_stores`.`supported_currencies`, `spree_stores`.`facebook`, `spree_stores`.`twitter`, `spree_stores`.`instagram`, `spree_stores`.`default_locale`, `spree_stores`.`customer_support_email`, `spree_stores`.`default_country_id`, `spree_stores`.`description`, `spree_stores`.`address`, `spree_stores`.`contact_phone`, `spree_stores`.`checkout_zone_id`, `spree_stores`.`seo_robots`, `spree_stores`.`supported_locales` FROM `spree_stores` WHERE (url like '%spree.internal%') ORDER BY `spree_stores`.`created_at` ASC LIMIT ?", 1),
                new PQuery("SELECT `spree_users`.* FROM `spree_users` WHERE `spree_users`.`deleted_at` IS NULL AND `spree_users`.`id` = ? ORDER BY `spree_users`.`id` ASC LIMIT ?", 82000001, 1),
//                new PQuery("SELECT `spree_orders`.* FROM `spree_orders` WHERE `spree_orders`.`store_id` = ? AND `spree_orders`.`completed_at` IS NULL AND `spree_orders`.`currency` = ? AND `spree_orders`.`token` = ? LIMIT ?", 1, "USD", "0vm4Crp3w7avKavcKrjzow1637694716396", 1), new PQuery("SELECT `spree_line_items`.* FROM `spree_line_items` WHERE `spree_line_items`.`order_id` = ? ORDER BY `spree_line_items`.`created_at` ASC", 25000005),
//                new PQuery("SELECT `spree_variants`.* FROM `spree_variants` WHERE `spree_variants`.`id` IN (?, ?, ?)", 83000136, 83000191, 83000198),
//                new PQuery("SELECT `spree_assets`.* FROM `spree_assets` WHERE `spree_assets`.`viewable_type` = ? AND `spree_assets`.`viewable_id` IN (?, ?, ?) ORDER BY `spree_assets`.`position` ASC", "Spree::Variant", 83000136, 83000191, 83000198),
                new PQuery("SELECT `spree_orders`.* FROM `spree_orders` WHERE `spree_orders`.`store_id` = ? AND `spree_orders`.`number` = ? AND (`spree_orders`.`user_id` = ? OR `spree_orders`.`token` = ?) LIMIT ?", 1, "R713119258", 82000001, "0vm4Crp3w7avKavcKrjzow1637694716396", 1),
                new PQuery("SELECT `spree_line_items`.* FROM `spree_line_items` WHERE `spree_line_items`.`order_id` = ? ORDER BY `spree_line_items`.`created_at` ASC", 25000004),
                new PQuery("SELECT `spree_variants`.* FROM `spree_variants` WHERE `spree_variants`.`id` IN (?, ?, ?, ?)", 83000220, 83000117, 83000203, 83000134),
                new PQuery("SELECT `mv`.* FROM `spree_variants` `mv` INNER JOIN `spree_variants` `ov` ON `mv`.`product_id` = `ov`.`product_id` WHERE `mv`.`deleted_at` IS NULL AND `mv`.`is_master` = true AND `ov`.`id` = ?", 83000220),
                new PQuery("SELECT `spree_assets`.* FROM `spree_assets` INNER JOIN `spree_variants` `mv` ON `spree_assets`.`viewable_id` = `mv`.`id` AND `spree_assets`.`viewable_type` = 'Spree::Variant' INNER JOIN `spree_variants` `ov` ON `mv`.`product_id` = `ov`.`product_id` WHERE `mv`.`deleted_at` IS NULL AND `mv`.`is_master` = true AND `ov`.`id` = ?", 83000220),
        };
        testQueries(queries, PARAMS, 1);
    }
}
