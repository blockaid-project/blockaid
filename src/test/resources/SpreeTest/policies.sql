-- We keep the `new_order_notifications_email` field non-public -- it's probably the store admin's email.
SELECT `id`,
       `name`,
       `url`,
       `meta_description`,
       `meta_keywords`,
       `seo_title`,
       `mail_from_address`,
       `default_currency`,
       `code`,
       `default`,
       `created_at`,
       `updated_at`,
       `supported_currencies`,
       `facebook`,
       `twitter`,
       `instagram`,
       `default_locale`,
       `customer_support_email`,
       `default_country_id`,
       `description`,
       `address`,
       `contact_phone`,
       `checkout_zone_id`,
       `seo_robots`,
       `supported_locales`
FROM `spree_stores`
WHERE (`url` LIKE _STORE_URL_PATTERN);
-- The maximum `updated_at` of all stores is used to compute `spree_menu_cache_key`.
SELECT `id`, `updated_at`
FROM `spree_stores`;

-- Information on deleted users shouldn't be accessible.
SELECT `spree_users`.*
FROM `spree_users`
WHERE `spree_users`.`deleted_at` IS NULL
  AND `spree_users`.`id` = _MY_UID;

-- The token is stored as a signed cookie and identifies the current order
-- (possibly from a user who is not signed in).
SELECT `spree_orders`.*
FROM `spree_orders`
         INNER JOIN `spree_stores` ON `spree_orders`.`store_id` = `spree_stores`.`id`
WHERE `spree_stores`.`url` LIKE _STORE_URL_PATTERN
  AND `spree_orders`.`token` = _TOKEN;
SELECT `spree_orders`.*
FROM `spree_orders`
         INNER JOIN `spree_users` ON `spree_orders`.`user_id` = `spree_users`.`id`
         INNER JOIN `spree_stores` ON `spree_orders`.`store_id` = `spree_stores`.`id`
WHERE `spree_users`.`id` = _MY_UID
  AND `spree_users`.`deleted_at` IS NULL
  AND `spree_stores`.`url` LIKE _STORE_URL_PATTERN;

SELECT `spree_role_users`.*
FROM `spree_role_users`
         INNER JOIN `spree_users` ON `spree_role_users`.`user_id` = `spree_users`.`id`
WHERE `spree_users`.`id` = _MY_UID
  AND `spree_users`.`deleted_at` IS NULL;
SELECT `spree_roles`.*
FROM `spree_roles`,
     `spree_role_users`,
     `spree_users`
WHERE `spree_roles`.`id` = `spree_role_users`.`role_id`
  AND `spree_role_users`.`user_id` = `spree_users`.`id`
  AND `spree_users`.`id` = _MY_UID
  AND `spree_users`.`deleted_at` IS NULL;

SELECT `spree_preferences`.*
FROM `spree_preferences`;

-- TODO(zhangwen): Should we hide revoked access tokens or those that expire?
-- Here's an example query:
-- SELECT `spree_oauth_access_tokens`.* FROM `spree_oauth_access_tokens` WHERE `spree_oauth_access_tokens`.`resource_owner_id` = 2 AND `spree_oauth_access_tokens`.`revoked_at` IS NULL AND `spree_oauth_access_tokens`.`expires_in` IS NULL ORDER BY `spree_oauth_access_tokens`.`id` DESC LIMIT 1
SELECT `spree_oauth_access_tokens`.*
FROM `spree_oauth_access_tokens`
         INNER JOIN `spree_users` ON `spree_oauth_access_tokens`.`resource_owner_id` = `spree_users`.`id`
WHERE `spree_users`.`id` = _MY_UID
  AND `spree_users`.`deleted_at` IS NULL;

SELECT `spree_store_credits`.*
FROM `spree_store_credits`,
     `spree_users`,
     `spree_stores`
WHERE `spree_store_credits`.`deleted_at` IS NULL
  AND `spree_store_credits`.`user_id` = `spree_users`.`id`
  AND `spree_users`.`id` = _MY_UID
  AND `spree_users`.`deleted_at` IS NULL
  AND `spree_store_credits`.`store_id` = `spree_stores`.`id`
  AND `spree_stores`.`url` LIKE _STORE_URL_PATTERN;

SELECT `spree_addresses`.*
FROM `spree_addresses`
         INNER JOIN `spree_users` ON `spree_addresses`.`user_id` = `spree_users`.`id`
WHERE `spree_addresses`.`deleted_at` IS NULL
  AND `spree_users`.`id` = _MY_UID
  AND `spree_users`.`deleted_at` IS NULL;

SELECT `spree_states`.*
FROM `spree_states`;
SELECT `spree_countries`.*
FROM `spree_countries`;

SELECT `spree_cms_pages`.*
FROM `spree_cms_pages`,
     `spree_stores`
WHERE `spree_cms_pages`.`deleted_at` IS NULL
  AND `spree_cms_pages`.`visible` = TRUE
  AND `spree_cms_pages`.`store_id` = `spree_stores`.`id`
  AND `spree_stores`.`url` LIKE _STORE_URL_PATTERN;

SELECT `spree_menus`.*
FROM `spree_menus`,
     `spree_stores`
WHERE `spree_menus`.`store_id` = `spree_stores`.`id`
  AND `spree_stores`.`url` LIKE _STORE_URL_PATTERN;

SELECT `spree_menu_items`.*
FROM `spree_menu_items`,
     `spree_menus`,
     `spree_stores`
WHERE `spree_menu_items`.`menu_id` = `spree_menus`.`id`
  AND `spree_menus`.`store_id` = `spree_stores`.`id`
  AND `spree_stores`.`url` LIKE _STORE_URL_PATTERN;

SELECT `spree_cms_sections`.*
FROM `spree_cms_sections`,
     `spree_cms_pages`,
     `spree_stores`
WHERE `spree_cms_sections`.`cms_page_id` = `spree_cms_pages`.`id`
  AND `spree_cms_pages`.`deleted_at` IS NULL
  AND `spree_cms_pages`.`visible` = TRUE
  AND `spree_cms_pages`.`store_id` = `spree_stores`.`id`
  AND `spree_stores`.`url` LIKE _STORE_URL_PATTERN;

SELECT `active_storage_attachments`.*
FROM `active_storage_attachments`,
     `spree_stores`
WHERE `active_storage_attachments`.`record_type` = 'Spree::Store'
  AND
  -- `active_storage_attachments`.`name` = 'favicon_image' AND
    `active_storage_attachments`.`record_id` = `spree_stores`.`id`
  AND `spree_stores`.`url` LIKE _STORE_URL_PATTERN;

SELECT `active_storage_attachments`.*
FROM `active_storage_attachments`,
     `spree_cms_sections`,
     `spree_cms_pages`,
     `spree_stores`
WHERE `active_storage_attachments`.`record_type` = 'Spree::CmsSection'
  AND `active_storage_attachments`.`record_id` = `spree_cms_sections`.`id`
  AND `spree_cms_sections`.`cms_page_id` = `spree_cms_pages`.`id`
  AND `spree_cms_pages`.`deleted_at` IS NULL
  AND `spree_cms_pages`.`visible` = TRUE
  AND `spree_cms_pages`.`store_id` = `spree_stores`.`id`
  AND `spree_stores`.`url` LIKE _STORE_URL_PATTERN;

SELECT `spree_taxonomies`.*
FROM `spree_taxonomies`,
     `spree_stores`
WHERE `spree_taxonomies`.`store_id` = `spree_stores`.`id`
  AND `spree_stores`.`url` LIKE _STORE_URL_PATTERN;

SELECT `spree_taxons`.*
FROM `spree_taxons`,
     `spree_taxonomies`,
     `spree_stores`
WHERE `spree_taxons`.`taxonomy_id` = `spree_taxonomies`.`id`
  AND `spree_taxonomies`.`store_id` = `spree_stores`.`id`
  AND `spree_stores`.`url` LIKE _STORE_URL_PATTERN;

SELECT spree_products_stores.*
FROM spree_products_stores,
     spree_stores
WHERE spree_products_stores.store_id = spree_stores.id
  AND spree_stores.url LIKE _STORE_URL_PATTERN;

-- Confirmed that Spree doesn't allow viewing products whose (1) `available_on` is null,
-- (2) `available_on` is later than the current time, or (3) `discontinue_on` is earlier than the current time.
SELECT `spree_products`.*
FROM `spree_products`
         INNER JOIN `spree_products_stores` ON `spree_products`.`id` = `spree_products_stores`.`product_id`
         INNER JOIN `spree_stores` ON `spree_products_stores`.`store_id` = `spree_stores`.`id`
WHERE (`spree_products`.deleted_at IS NULL OR `spree_products`.deleted_at > _NOW)
  AND (`spree_products`.discontinue_on IS NULL OR `spree_products`.discontinue_on > _NOW)
  AND (`spree_products`.available_on < _NOW)
  AND `spree_stores`.`url` LIKE _STORE_URL_PATTERN;
-- A product is also visible if one of its variants is in the current cart, even if it's unavailable or discontinued.
SELECT *
FROM `spree_products`
         INNER JOIN `spree_variants` ON `spree_products`.`id` = `spree_variants`.`product_id`
         INNER JOIN `spree_line_items` ON `spree_line_items`.`variant_id` = `spree_variants`.`id`
         INNER JOIN `spree_orders` ON `spree_orders`.`id` = `spree_line_items`.`order_id`
         INNER JOIN `spree_stores` ON `spree_orders`.`store_id` = `spree_stores`.`id`
WHERE `spree_stores`.`url` LIKE _STORE_URL_PATTERN
  AND `spree_orders`.`token` = _TOKEN;
SELECT *
FROM `spree_products`
         INNER JOIN `spree_variants` ON `spree_products`.`id` = `spree_variants`.`product_id`
         INNER JOIN `spree_line_items` ON `spree_line_items`.`variant_id` = `spree_variants`.`id`
         INNER JOIN `spree_orders` ON `spree_line_items`.`order_id` = `spree_orders`.`id`
         INNER JOIN `spree_users` ON `spree_orders`.`user_id` = `spree_users`.`id`
         INNER JOIN `spree_stores` ON `spree_orders`.`store_id` = `spree_stores`.`id`
WHERE `spree_users`.`id` = _MY_UID
  AND `spree_users`.`deleted_at` IS NULL
  AND `spree_stores`.`url` LIKE _STORE_URL_PATTERN;

-- TODO(zhangwen): This is a monstrosity.  We need better ergonomics.
--   Something like: If a product is visible, so should its variants be.
SELECT `spree_promotions`.*
FROM `spree_promotions`
         INNER JOIN `spree_promotion_rules` ON `spree_promotions`.`id` = `spree_promotion_rules`.`promotion_id`
         INNER JOIN `spree_product_promotion_rules`
                    ON `spree_promotion_rules`.`id` = `spree_product_promotion_rules`.`promotion_rule_id`
         INNER JOIN `spree_products` ON `spree_product_promotion_rules`.`product_id` = `spree_products`.`id`
         INNER JOIN `spree_products_stores` ON `spree_products`.`id` = `spree_products_stores`.`product_id`
         INNER JOIN `spree_stores` ON `spree_products_stores`.`store_id` = `spree_stores`.`id`
WHERE `spree_promotions`.`advertise` = TRUE
  AND (spree_promotions.starts_at IS NULL OR spree_promotions.starts_at < _NOW)
  AND (spree_promotions.expires_at IS NULL OR spree_promotions.expires_at > _NOW)
  AND (`spree_products`.deleted_at IS NULL OR `spree_products`.deleted_at > _NOW)
  AND (`spree_products`.discontinue_on IS NULL OR `spree_products`.discontinue_on > _NOW)
  AND (`spree_products`.available_on < _NOW)
  AND `spree_stores`.`url` LIKE _STORE_URL_PATTERN;

SELECT `spree_variants`.*
FROM `spree_variants`
         INNER JOIN `spree_products` ON `spree_variants`.`product_id` = `spree_products`.`id`
         INNER JOIN `spree_products_stores` ON `spree_products`.`id` = `spree_products_stores`.`product_id`
         INNER JOIN `spree_stores` ON `spree_products_stores`.`store_id` = `spree_stores`.`id`
WHERE `spree_variants`.`deleted_at` IS NULL
  -- The master variant is always visible, it seems.
  AND (`spree_variants`.`is_master` = TRUE
    -- Other variants are visible if not discontinued.
    OR `spree_variants`.`discontinue_on` IS NULL
    OR `spree_variants`.`discontinue_on` > _NOW)
  AND `spree_products`.`deleted_at` IS NULL
  AND (`spree_products`.deleted_at IS NULL OR `spree_products`.deleted_at > _NOW)
  AND (`spree_products`.discontinue_on IS NULL OR `spree_products`.discontinue_on > _NOW)
  AND (`spree_products`.available_on < _NOW)
  AND `spree_stores`.`url` LIKE _STORE_URL_PATTERN;
-- A variant is visible if it's in the user's order, even if the variant is discontinued / no longer available, etc.
-- In the discontinued / unavailable case, the "orders" page still lists the item and but says "out of stock".
SELECT `spree_variants`.*
FROM `spree_variants`
         INNER JOIN `spree_line_items` ON `spree_line_items`.`variant_id` = `spree_variants`.`id`
         INNER JOIN `spree_orders` ON `spree_orders`.`id` = `spree_line_items`.`order_id`
         INNER JOIN `spree_stores` ON `spree_orders`.`store_id` = `spree_stores`.`id`
WHERE `spree_stores`.`url` LIKE _STORE_URL_PATTERN
  AND `spree_orders`.`token` = _TOKEN;
SELECT `spree_variants`.*
FROM `spree_variants`
         INNER JOIN `spree_line_items` ON `spree_line_items`.`variant_id` = `spree_variants`.`id`
         INNER JOIN `spree_orders` ON `spree_line_items`.`order_id` = `spree_orders`.`id`
         INNER JOIN `spree_users` ON `spree_orders`.`user_id` = `spree_users`.`id`
         INNER JOIN `spree_stores` ON `spree_orders`.`store_id` = `spree_stores`.`id`
WHERE `spree_users`.`id` = _MY_UID
  AND `spree_users`.`deleted_at` IS NULL
  AND `spree_stores`.`url` LIKE _STORE_URL_PATTERN;

SELECT `spree_assets`.*
FROM `spree_assets`
         INNER JOIN `spree_variants`
                    ON `spree_assets`.`viewable_type` = 'Spree::Variant' AND
                       `spree_assets`.`viewable_id` = `spree_variants`.`id`
         INNER JOIN `spree_products` ON `spree_variants`.`product_id` = `spree_products`.`id`
         INNER JOIN `spree_products_stores` ON `spree_products`.`id` = `spree_products_stores`.`product_id`
         INNER JOIN `spree_stores` ON `spree_products_stores`.`store_id` = `spree_stores`.`id`
WHERE `spree_variants`.`deleted_at` IS NULL
  AND (`spree_variants`.`is_master` = TRUE
    OR `spree_variants`.`discontinue_on` IS NULL
    OR `spree_variants`.`discontinue_on` > _NOW)
  AND (`spree_products`.deleted_at IS NULL OR `spree_products`.deleted_at > _NOW)
  AND (`spree_products`.discontinue_on IS NULL OR `spree_products`.discontinue_on > _NOW)
  AND (`spree_products`.available_on < _NOW)
  AND `spree_stores`.`url` LIKE _STORE_URL_PATTERN;
SELECT `spree_assets`.*
FROM `spree_assets`
         INNER JOIN `spree_variants`
                    ON `spree_assets`.`viewable_type` = 'Spree::Variant' AND
                       `spree_assets`.`viewable_id` = `spree_variants`.`id`
         INNER JOIN `spree_line_items` ON `spree_line_items`.`variant_id` = `spree_variants`.`id`
         INNER JOIN `spree_orders` ON `spree_orders`.`id` = `spree_line_items`.`order_id`
         INNER JOIN `spree_stores` ON `spree_orders`.`store_id` = `spree_stores`.`id`
WHERE `spree_stores`.`url` LIKE _STORE_URL_PATTERN
  AND `spree_orders`.`token` = _TOKEN;
SELECT `spree_assets`.*
FROM `spree_assets`
         INNER JOIN `spree_variants`
                    ON `spree_assets`.`viewable_type` = 'Spree::Variant' AND
                       `spree_assets`.`viewable_id` = `spree_variants`.`id`
         INNER JOIN `spree_line_items` ON `spree_line_items`.`variant_id` = `spree_variants`.`id`
         INNER JOIN `spree_orders` ON `spree_line_items`.`order_id` = `spree_orders`.`id`
         INNER JOIN `spree_users` ON `spree_orders`.`user_id` = `spree_users`.`id`
         INNER JOIN `spree_stores` ON `spree_orders`.`store_id` = `spree_stores`.`id`
WHERE `spree_users`.`id` = _MY_UID
  AND `spree_users`.`deleted_at` IS NULL
  AND `spree_stores`.`url` LIKE _STORE_URL_PATTERN;

SELECT `spree_prices`.*
FROM `spree_prices`
         INNER JOIN `spree_variants` ON `spree_prices`.`variant_id` = `spree_variants`.`id`
         INNER JOIN `spree_products` ON `spree_variants`.`product_id` = `spree_products`.`id`
         INNER JOIN `spree_products_stores` ON `spree_products`.`id` = `spree_products_stores`.`product_id`
         INNER JOIN `spree_stores` ON `spree_products_stores`.`store_id` = `spree_stores`.`id`
WHERE `spree_prices`.`deleted_at` IS NULL
  AND `spree_variants`.`deleted_at` IS NULL
  AND (`spree_variants`.`is_master` = TRUE
    OR `spree_variants`.`discontinue_on` IS NULL
    OR `spree_variants`.`discontinue_on` > _NOW)
  AND (`spree_products`.deleted_at IS NULL OR `spree_products`.deleted_at > _NOW)
  AND (`spree_products`.discontinue_on IS NULL OR `spree_products`.discontinue_on > _NOW)
  AND (`spree_products`.available_on < _NOW)
  AND `spree_stores`.`url` LIKE _STORE_URL_PATTERN;

-- These two tables don't seem sensitive.  In particular, they're not tied to any variant.
SELECT `spree_option_values`.*
FROM `spree_option_values`;
SELECT `spree_option_types`.*
FROM `spree_option_types`;

SELECT `spree_option_value_variants`.*
FROM `spree_option_value_variants`
         INNER JOIN `spree_variants` ON `spree_option_value_variants`.`variant_id` = `spree_variants`.`id`
         INNER JOIN `spree_products` ON `spree_variants`.`product_id` = `spree_products`.`id`
         INNER JOIN `spree_products_stores` ON `spree_products`.`id` = `spree_products_stores`.`product_id`
         INNER JOIN `spree_stores` ON `spree_products_stores`.`store_id` = `spree_stores`.`id`
WHERE `spree_variants`.`deleted_at` IS NULL
  AND (`spree_variants`.`is_master` = TRUE
    OR `spree_variants`.`discontinue_on` IS NULL
    OR `spree_variants`.`discontinue_on` > _NOW)
  AND (`spree_products`.deleted_at IS NULL OR `spree_products`.deleted_at > _NOW)
  AND (`spree_products`.discontinue_on IS NULL OR `spree_products`.discontinue_on > _NOW)
  AND (`spree_products`.available_on < _NOW)
  AND `spree_stores`.`url` LIKE _STORE_URL_PATTERN;
SELECT `spree_option_value_variants`.*
FROM `spree_option_value_variants`
         INNER JOIN `spree_variants` ON `spree_option_value_variants`.`variant_id` = `spree_variants`.`id`
         INNER JOIN `spree_line_items` ON `spree_line_items`.`variant_id` = `spree_variants`.`id`
         INNER JOIN `spree_orders` ON `spree_orders`.`id` = `spree_line_items`.`order_id`
         INNER JOIN `spree_stores` ON `spree_orders`.`store_id` = `spree_stores`.`id`
WHERE `spree_stores`.`url` LIKE _STORE_URL_PATTERN
  AND `spree_orders`.`token` = _TOKEN;
SELECT `spree_option_value_variants`.*
FROM `spree_option_value_variants`
         INNER JOIN `spree_variants` ON `spree_option_value_variants`.`variant_id` = `spree_variants`.`id`
         INNER JOIN `spree_line_items` ON `spree_line_items`.`variant_id` = `spree_variants`.`id`
         INNER JOIN `spree_orders` ON `spree_line_items`.`order_id` = `spree_orders`.`id`
         INNER JOIN `spree_users` ON `spree_orders`.`user_id` = `spree_users`.`id`
         INNER JOIN `spree_stores` ON `spree_orders`.`store_id` = `spree_stores`.`id`
WHERE `spree_users`.`id` = _MY_UID
  AND `spree_users`.`deleted_at` IS NULL
  AND `spree_stores`.`url` LIKE _STORE_URL_PATTERN;

SELECT `spree_line_items`.*
FROM `spree_line_items`
         INNER JOIN `spree_orders` ON `spree_line_items`.`order_id` = `spree_orders`.`id`
         INNER JOIN `spree_stores` ON `spree_orders`.`store_id` = `spree_stores`.`id`
WHERE `spree_orders`.`token` = _TOKEN
  AND `spree_stores`.`url` LIKE _STORE_URL_PATTERN;
SELECT `spree_line_items`.*
FROM `spree_line_items`
         INNER JOIN `spree_orders` ON `spree_line_items`.`order_id` = `spree_orders`.`id`
         INNER JOIN `spree_users` ON `spree_orders`.`user_id` = `spree_users`.`id`
         INNER JOIN `spree_stores` ON `spree_orders`.`store_id` = `spree_stores`.`id`
WHERE `spree_users`.`id` = _MY_UID
  AND `spree_users`.`deleted_at` IS NULL
  AND `spree_stores`.`url` LIKE _STORE_URL_PATTERN;

-- TODO(zhangwen): Should the `eligible` column affect visibility?
SELECT `spree_adjustments`.*
FROM `spree_adjustments`
         INNER JOIN `spree_orders` ON (`spree_adjustments`.`adjustable_type` = 'Spree::Order' AND
                                       `spree_adjustments`.`adjustable_id` = `spree_orders`.`id`) OR
                                      `spree_adjustments`.`order_id` = `spree_orders`.`id`
         INNER JOIN `spree_stores` ON `spree_orders`.`store_id` = `spree_stores`.`id`
WHERE `spree_stores`.`url` LIKE _STORE_URL_PATTERN
  AND `spree_orders`.`token` = _TOKEN;
SELECT `spree_adjustments`.*
FROM `spree_adjustments`
         INNER JOIN `spree_orders` ON (`spree_adjustments`.`adjustable_type` = 'Spree::Order' AND
                                       `spree_adjustments`.`adjustable_id` = `spree_orders`.`id`) OR
                                      `spree_adjustments`.`order_id` = `spree_orders`.`id`
         INNER JOIN `spree_users` ON `spree_orders`.`user_id` = `spree_users`.`id`
         INNER JOIN `spree_stores` ON `spree_orders`.`store_id` = `spree_stores`.`id`
WHERE `spree_users`.`id` = _MY_UID
  AND `spree_users`.`deleted_at` IS NULL
  AND `spree_stores`.`url` LIKE _STORE_URL_PATTERN;

SELECT `spree_stock_items`.*
FROM `spree_stock_items`
         INNER JOIN `spree_stock_locations` ON `spree_stock_locations`.`id` = `spree_stock_items`.`stock_location_id`
         INNER JOIN `spree_variants` ON `spree_variants`.`id` = `spree_stock_items`.`variant_id`
         INNER JOIN `spree_line_items` ON `spree_line_items`.`variant_id` = `spree_variants`.`id`
         INNER JOIN `spree_orders` ON `spree_orders`.`id` = `spree_line_items`.`order_id`
         INNER JOIN `spree_stores` ON `spree_orders`.`store_id` = `spree_stores`.`id`
WHERE `spree_stock_items`.`deleted_at` IS NULL
  AND `spree_stock_locations`.`active` = true
  AND `spree_stores`.`url` LIKE _STORE_URL_PATTERN
  AND `spree_orders`.`token` = _TOKEN;
SELECT `spree_stock_items`.*
FROM `spree_stock_items`
         INNER JOIN `spree_stock_locations` ON `spree_stock_locations`.`id` = `spree_stock_items`.`stock_location_id`
         INNER JOIN `spree_variants` ON `spree_variants`.`id` = `spree_stock_items`.`variant_id`
         INNER JOIN `spree_line_items` ON `spree_line_items`.`variant_id` = `spree_variants`.`id`
         INNER JOIN `spree_orders` ON `spree_orders`.`id` = `spree_line_items`.`order_id`
         INNER JOIN `spree_users` ON `spree_orders`.`user_id` = `spree_users`.`id`
         INNER JOIN `spree_stores` ON `spree_orders`.`store_id` = `spree_stores`.`id`
WHERE `spree_stock_items`.`deleted_at` IS NULL
  AND `spree_stock_locations`.`active` = true
  AND `spree_users`.`id` = _MY_UID
  AND `spree_users`.`deleted_at` IS NULL
  AND `spree_stores`.`url` LIKE _STORE_URL_PATTERN;
