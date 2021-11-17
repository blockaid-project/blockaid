-- We keep the `new_order_notifications_email` field non-public -- it's probably the store admin's email.
SELECT `id`, `name`, `url`, `meta_description`, `meta_keywords`, `seo_title`, `mail_from_address`, `default_currency`,
       `code`, `default`, `created_at`, `updated_at`, `supported_currencies`, `facebook`, `twitter`, `instagram`,
       `default_locale`, `customer_support_email`, `default_country_id`, `description`, `address`, `contact_phone`,
       `checkout_zone_id`, `seo_robots`, `supported_locales`
FROM `spree_stores` WHERE (`url` LIKE _STORE_URL_PATTERN);
-- The maximum `updated_at` of all stores is used to compute `spree_menu_cache_key`.
SELECT `id`, `updated_at` FROM `spree_stores`;

-- Information on deleted users shouldn't be accessible.
SELECT `spree_users`.* FROM `spree_users` WHERE `spree_users`.`deleted_at` IS NULL AND `spree_users`.`id` = _MY_UID;

-- The token is stored as a signed cookie and identifies the current order
-- (possibly from a user who is not signed in).
SELECT `spree_orders`.* FROM `spree_orders`, `spree_stores`
WHERE `spree_orders`.`store_id` = `spree_stores`.`id` AND
      `spree_stores`.`url` LIKE _STORE_URL_PATTERN AND
      `spree_orders`.`token` = _TOKEN;
SELECT `spree_orders`.* FROM `spree_orders`, `spree_users`, `spree_stores`
WHERE `spree_orders`.`user_id` = `spree_users`.`id` AND
      `spree_users`.`id` = _MY_UID AND
      `spree_users`.`deleted_at` IS NULL AND
      `spree_orders`.`store_id` = `spree_stores`.`id` AND
      `spree_stores`.`url` LIKE _STORE_URL_PATTERN;

SELECT `spree_role_users`.* FROM `spree_role_users`
    INNER JOIN `spree_users` ON `spree_role_users`.`user_id` = `spree_users`.`id`
WHERE `spree_users`.`id` = _MY_UID AND `spree_users`.`deleted_at` IS NULL;
SELECT `spree_roles`.* FROM `spree_roles`, `spree_role_users`, `spree_users`
WHERE `spree_roles`.`id` = `spree_role_users`.`role_id` AND
      `spree_role_users`.`user_id` = `spree_users`.`id` AND
      `spree_users`.`id` = _MY_UID AND
      `spree_users`.`deleted_at` IS NULL;

SELECT `spree_preferences`.* FROM `spree_preferences`;

-- TODO(zhangwen): Should we hide revoked access tokens or those that expire?
-- Here's an example query:
-- SELECT `spree_oauth_access_tokens`.* FROM `spree_oauth_access_tokens` WHERE `spree_oauth_access_tokens`.`resource_owner_id` = 2 AND `spree_oauth_access_tokens`.`revoked_at` IS NULL AND `spree_oauth_access_tokens`.`expires_in` IS NULL ORDER BY `spree_oauth_access_tokens`.`id` DESC LIMIT 1
SELECT `spree_oauth_access_tokens`.* FROM `spree_oauth_access_tokens`
    INNER JOIN `spree_users` ON `spree_oauth_access_tokens`.`resource_owner_id` = `spree_users`.`id`
WHERE `spree_users`.`id` = _MY_UID AND `spree_users`.`deleted_at` IS NULL;

-- TODO(zhangwen): Limit disclosure to current store?
SELECT `spree_store_credits`.* FROM `spree_store_credits`, `spree_users`, `spree_stores`
WHERE `spree_store_credits`.`deleted_at` IS NULL AND
        `spree_store_credits`.`user_id` = `spree_users`.`id` AND
        `spree_users`.`id` = _MY_UID AND `spree_users`.`deleted_at` IS NULL AND
        `spree_store_credits`.`store_id` = `spree_stores`.`id` AND
        `spree_stores`.`url` LIKE _STORE_URL_PATTERN;

SELECT `spree_addresses`.* FROM `spree_addresses`
    INNER JOIN `spree_users` ON `spree_addresses`.`user_id` = `spree_users`.`id`
WHERE `spree_addresses`.`deleted_at` IS NULL AND
      `spree_users`.`id` = _MY_UID AND `spree_users`.`deleted_at` IS NULL;

SELECT `spree_states`.* FROM `spree_states`;
SELECT `spree_countries`.* FROM `spree_countries`;

SELECT `spree_cms_pages`.* FROM `spree_cms_pages`, `spree_stores`
WHERE `spree_cms_pages`.`deleted_at` IS NULL AND `spree_cms_pages`.`visible` = TRUE AND
      `spree_cms_pages`.`store_id` = `spree_stores`.`id` AND `spree_stores`.`url` LIKE _STORE_URL_PATTERN;

SELECT `spree_menus`.* FROM `spree_menus`, `spree_stores`
WHERE `spree_menus`.`store_id` = `spree_stores`.`id` AND
      `spree_stores`.`url` LIKE _STORE_URL_PATTERN;

SELECT `spree_menu_items`.* FROM `spree_menu_items`, `spree_menus`, `spree_stores`
WHERE `spree_menu_items`.`menu_id` = `spree_menus`.`id` AND
      `spree_menus`.`store_id` = `spree_stores`.`id` AND
      `spree_stores`.`url` LIKE _STORE_URL_PATTERN;

SELECT `spree_cms_sections`.* FROM `spree_cms_sections`, `spree_cms_pages`, `spree_stores`
WHERE `spree_cms_sections`.`cms_page_id` = `spree_cms_pages`.`id` AND
      `spree_cms_pages`.`deleted_at` IS NULL AND `spree_cms_pages`.`visible` = TRUE AND
      `spree_cms_pages`.`store_id` = `spree_stores`.`id` AND `spree_stores`.`url` LIKE _STORE_URL_PATTERN;

SELECT `active_storage_attachments`.* FROM `active_storage_attachments`, `spree_stores`
WHERE `active_storage_attachments`.`record_type` = 'Spree::Store' AND
      -- `active_storage_attachments`.`name` = 'favicon_image' AND
      `active_storage_attachments`.`record_id` = `spree_stores`.`id` AND
      `spree_stores`.`url` LIKE _STORE_URL_PATTERN;

SELECT `active_storage_attachments`.*
FROM `active_storage_attachments`, `spree_cms_sections`, `spree_cms_pages`, `spree_stores`
WHERE `active_storage_attachments`.`record_type` = 'Spree::CmsSection' AND
      `active_storage_attachments`.`record_id` = `spree_cms_sections`.`id` AND
      `spree_cms_sections`.`cms_page_id` = `spree_cms_pages`.`id` AND
      `spree_cms_pages`.`deleted_at` IS NULL AND `spree_cms_pages`.`visible` = TRUE AND
      `spree_cms_pages`.`store_id` = `spree_stores`.`id` AND `spree_stores`.`url` LIKE _STORE_URL_PATTERN;

SELECT `spree_taxonomies`.* FROM `spree_taxonomies`, `spree_stores`
WHERE `spree_taxonomies`.`store_id` = `spree_stores`.`id` AND `spree_stores`.`url` LIKE _STORE_URL_PATTERN;

SELECT `spree_taxons`.* FROM `spree_taxons`, `spree_taxonomies`, `spree_stores`
WHERE `spree_taxons`.`taxonomy_id` = `spree_taxonomies`.`id` AND
      `spree_taxonomies`.`store_id` = `spree_stores`.`id` AND
      `spree_stores`.`url` LIKE _STORE_URL_PATTERN;

SELECT spree_products_stores.* FROM spree_products_stores, spree_stores
WHERE spree_products_stores.store_id = spree_stores.id AND
      spree_stores.url LIKE _STORE_URL_PATTERN;

SELECT `spree_products`.* FROM `spree_products`, `spree_products_stores`, `spree_stores`
WHERE `spree_products`.`id` = `spree_products_stores`.`product_id` AND
      `spree_products`.`deleted_at` IS NULL AND
      `spree_products_stores`.`store_id` = `spree_stores`.`id` AND
      (`spree_products`.deleted_at IS NULL OR `spree_products`.deleted_at > _NOW) AND
      (`spree_products`.discontinue_on IS NULL OR `spree_products`.discontinue_on > _NOW) AND
      (`spree_products`.available_on < _NOW) AND
      `spree_stores`.`url` LIKE _STORE_URL_PATTERN;

SELECT spree_promotions.* FROM spree_promotions;
SELECT spree_promotion_rules.* FROM spree_promotion_rules;
SELECT * FROM spree_promotion_categories;
